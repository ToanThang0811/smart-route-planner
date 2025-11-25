from flask import Flask, render_template, request, jsonify
import folium
import osmnx as ox
import networkx as nx
from geopy.distance import geodesic
import requests
import threading
import math
import os
import logging
from typing import Optional, Tuple, List, Dict, Any
from fuzzywuzzy import fuzz, process
import Levenshtein

app = Flask(__name__)

# Configuration
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

ox.settings.log_console = False
ox.settings.use_cache = True
ox.settings.timeout = 180

class OptimizedSpellChecker:
    def __init__(self):
        self.place_names = []
        self.common_corrections = self._load_common_corrections()
    
    def set_place_names(self, place_names: List[str]):
        """Set place names after geocoder is initialized"""
        self.place_names = place_names
    
    def _load_common_corrections(self):
        """Từ điển sửa lỗi phổ biến nhất"""
        return {
            # Lỗi phở
            'fò': 'phở', 'fở': 'phở', 'pho': 'phở', 'fó': 'phở',
            # Lỗi pasteur
            'paster': 'pasteur', 'pasteru': 'pasteur', 'pastuer': 'pasteur', 'pateur': 'pasteur',
            # Lỗi huỳnh hoa
            'huynh': 'huỳnh', 'huynhhoa': 'huỳnh hoa', 'huỳnhhoa': 'huỳnh hoa',
            # Lỗi coffee
            'coffe': 'coffee', 'cofee': 'coffee', 'cofe': 'coffee', 'highland': 'highlands',
            'highland coffee': 'highlands coffee',
            # Lỗi vincom
            'vincomcenter': 'vincom center', 'vincome': 'vincom', 'vincom landmak': 'vincom landmark',
            # Lỗi crescent
            'cresent': 'crescent', 'cresent mall': 'crescent mall',
            # Lỗi aeon
            'aeonmall': 'aeon mall', 'eon': 'aeon',
            # Lỗi bitexco
            'bitesco': 'bitexco', 'bitexo': 'bitexco',
            # Lỗi bệnh viện
            'bénh viện': 'bệnh viện', 'bệnh viên': 'bệnh viện', 'benh vien': 'bệnh viện', 'bệnhviện': 'bệnh viện',
            'choray': 'chợ rẫy', 'cho ray': 'chợ rẫy',
            # Lỗi đại học
            'đai học': 'đại học', 'dai hoc': 'đại học', 'daihoc': 'đại học', 'đạihọc': 'đại học',
            'bach khoa': 'bách khoa', 'báchkhoa': 'bách khoa',
            # Viết tắt
            'q1': 'quận 1', 'q.1': 'quận 1', 'q 1': 'quận 1', 'q2': 'quận 2', 'q3': 'quận 3', 
            'q4': 'quận 4', 'q5': 'quận 5', 'q6': 'quận 6', 'q7': 'quận 7', 'q8': 'quận 8',
            'q9': 'quận 9', 'q10': 'quận 10', 'q11': 'quận 11', 'q12': 'quận 12',
            'bt': 'bình thạnh', 'gv': 'gò vấp', 'td': 'thủ đức', 'tb': 'tân bình', 'tp': 'tân phú',
            'tphcm': 'hồ chí minh', 'hcm': 'hồ chí minh', 'sg': 'hồ chí minh', 'saigon': 'hồ chí minh',
            # Lỗi khác
            'trungtam': 'trung tâm', 'tttm': 'trung tâm thương mại', 'tt': 'trung tâm',
            'đt': 'đường', 'dt': 'đường', 'ng': 'nguyễn'
        }
    
    def smart_correct(self, text: str) -> str:
        """Sửa lỗi thông minh - TỐI ƯU NHẤT"""
        if not text or len(text.strip()) < 2:
            return text
            
        original = text
        text = text.lower().strip()
        
        # Bước 1: Sửa lỗi cứng với từ điển
        text = self._apply_common_corrections(text)
        
        # Bước 2: Fuzzy matching với địa danh nổi tiếng
        if self.place_names:
            text = self._fuzzy_match_places(text)
        
        # Bước 3: Chuẩn hóa viết hoa
        text = self._normalize_capitalization(text)
        
        if text != original.lower():
            logger.info(f"🔧 Optimized correction: '{original}' -> '{text}'")
        
        return text
    
    def _apply_common_corrections(self, text: str) -> str:
        """Áp dụng sửa lỗi từ từ điển"""
        words = text.split()
        corrected_words = []
        
        for word in words:
            if word in self.common_corrections:
                corrected_words.append(self.common_corrections[word])
            else:
                corrected_words.append(word)
        
        return ' '.join(corrected_words)
    
    def _fuzzy_match_places(self, text: str) -> str:
        """Tìm địa danh gần nhất bằng fuzzy matching"""
        if len(text) < 3:
            return text
        
        best_match, score = process.extractOne(text, self.place_names, scorer=fuzz.token_set_ratio)
        
        if score >= 85:
            return best_match
        elif score >= 70:
            logger.info(f"🎯 Fuzzy match: '{text}' -> '{best_match}' (score: {score})")
            return best_match
        
        return text
    
    def _normalize_capitalization(self, text: str) -> str:
        """Chuẩn hóa viết hoa tiếng Việt"""
        words = text.split()
        capitalized_words = []
        
        for word in words:
            if len(word) > 1:
                capitalized_words.append(word[0].upper() + word[1:])
            else:
                capitalized_words.append(word.upper())
        
        return ' '.join(capitalized_words)

class SmartGeocoder:
    def __init__(self):
        self.coords_cache = {}
        self.popular_places = self.load_popular_places()
        self.spell_checker = OptimizedSpellChecker()
        self.spell_checker.set_place_names(list(self.popular_places.keys()))
    
    def load_popular_places(self):
        """Tải danh sách địa điểm phổ biến TP.HCM"""
        return {
            # Quán ăn, Cafe
            'phở hòa pasteur': (10.7720, 106.6950),
            'bánh mì huỳnh hoa': (10.7640, 106.6900),
            'cơm tấm cali': (10.7750, 106.7000),
            'highlands coffee': (10.7757, 106.7000),
            'the coffee house': (10.7800, 106.7050),
            'phúc long': (10.7730, 106.6980),
            
            # Trung tâm thương mại
            'vincom center': (10.7820, 106.7000),
            'vincom landmark 81': (10.7950, 106.7220),
            'crescent mall': (10.7280, 106.7220),
            'aeon mall bình tân': (10.7350, 106.6170),
            
            # Bệnh viện
            'bệnh viện chợ rẫy': (10.7580, 106.6580),
            'bệnh viện gia định': (10.8018, 106.6585),
            'bệnh viện nhân dân 115': (10.7460, 106.6670),
            
            # Trường học
            'đại học bách khoa': (10.8804, 106.8050),
            'đại học khoa học tự nhiên': (10.7629, 106.6825),
            
            # Địa danh
            'chợ bến thành': (10.7720, 106.6980),
            'dinh độc lập': (10.7775, 106.6950),
            'nhà thờ đức bà': (10.7798, 106.6990),
            
            # Quận
            'quận 1': (10.7757, 106.7000), 'quận 2': (10.7872, 106.7490),
            'quận 3': (10.7823, 106.6860), 'quận 4': (10.7642, 106.7050),
            'quận 5': (10.7540, 106.6690), 'quận 6': (10.7464, 106.6350),
            'quận 7': (10.7324, 106.7260), 'quận 8': (10.7200, 106.6280),
            'quận 9': (10.8420, 106.7950), 'quận 10': (10.7679, 106.6660),
            'quận 11': (10.7630, 106.6460), 'quận 12': (10.8630, 106.6540),
            'bình thạnh': (10.8070, 106.7130), 'gò vấp': (10.8380, 106.6650),
            'phú nhuận': (10.7970, 106.6750), 'tân bình': (10.8010, 106.6520),
            'tân phú': (10.7900, 106.6280), 'thủ đức': (10.8494, 106.7710),
            'bình tân': (10.7650, 106.6030),
            
            # Khác
            'sân bay tân sơn nhất': (10.8180, 106.6520),
            'bến xe miền đông': (10.8310, 106.6290),
            'bitexco financial tower': (10.7718, 106.7042),
        }
    
    def smart_geocode(self, location: str) -> Optional[Tuple[float, float]]:
        """Geocoding thông minh với sửa lỗi chính tả"""
        if not location or len(location.strip()) < 2:
            return None
            
        location = location.strip()
        
        # Kiểm tra cache
        if location in self.coords_cache:
            return self.coords_cache[location]
        
        # Sửa lỗi chính tả
        corrected_location = self.spell_checker.smart_correct(location)
        
        if corrected_location != location:
            logger.info(f"🔧 Corrected: '{location}' -> '{corrected_location}'")
        
        # Tìm trong popular places
        if corrected_location.lower() in self.popular_places:
            coords = self.popular_places[corrected_location.lower()]
            self.coords_cache[location] = coords
            return coords
        
        # Geocoding fallback
        enhanced_addr = self._enhance_address(corrected_location)
        coords = self._geocode_with_osm(enhanced_addr)
        
        if coords:
            self.coords_cache[location] = coords
            return coords
            
        return None

    def _enhance_address(self, address: str) -> str:
        """Chuẩn hóa địa chỉ"""
        if not address:
            return address
            
        address_lower = address.lower()
        
        if not any(x in address_lower for x in ['hồ chí minh', 'hcm', 'tphcm']):
            address_lower = f"{address_lower}, Hồ Chí Minh, Vietnam"
        
        return address_lower.title()

    def _geocode_with_osm(self, address: str) -> Optional[Tuple[float, float]]:
        """Geocoding sử dụng Nominatim OSM"""
        try:
            url = "https://nominatim.openstreetmap.org/search"
            params = {'q': address, 'format': 'json', 'limit': 1, 'countrycodes': 'vn'}
            response = requests.get(url, params=params, timeout=10)
            
            if response.status_code == 200 and response.json():
                data = response.json()[0]
                return (float(data['lat']), float(data['lon']))
        except Exception as e:
            logger.warning(f"Geocoding failed: {e}")
            
        return None

class RoutePlanner:
    def __init__(self):
        self.coords_cache = {}
        self.graph = None
        self.geocoder = smart_geocoder
        self._init_graph()
    
    def _init_graph(self):
        def load_graph():
            try:
                logger.info("🗺️ Loading HCMC map...")
                self.graph = ox.graph_from_point(
                    (10.7757, 106.7000), dist=6000, network_type='drive', simplify=True
                )
                logger.info("✅ Map loaded successfully!")
            except Exception as e:
                logger.error(f"⚠ Map loading failed: {e}")
                self.graph = None
        
        threading.Thread(target=load_graph, daemon=True).start()

    def get_coordinates(self, location: str) -> Optional[Tuple[float, float]]:
        return self.geocoder.smart_geocode(location)

    def find_route(self, origin_coords: Tuple[float, float], 
                   destination_coords: Tuple[float, float]) -> Tuple[List, float]:
        if self.graph is None:
            return self._create_fallback_route(origin_coords, destination_coords)
        
        try:
            origin_node = ox.distance.nearest_nodes(self.graph, origin_coords[1], origin_coords[0])
            destination_node = ox.distance.nearest_nodes(self.graph, destination_coords[1], destination_coords[0])
            
            route = nx.shortest_path(self.graph, origin_node, destination_node, weight='length')
            route_coords = [[self.graph.nodes[node]['y'], self.graph.nodes[node]['x']] for node in route]
            
            distance = self._calculate_distance(route_coords)
            return route_coords, distance
            
        except Exception as e:
            logger.warning(f"Routing failed: {e}")
            return self._create_fallback_route(origin_coords, destination_coords)

    def _create_fallback_route(self, origin: Tuple[float, float], 
                              destination: Tuple[float, float]) -> Tuple[List, float]:
        lat1, lon1 = origin
        lat2, lon2 = destination
        
        num_points = max(10, int(geodesic(origin, destination).meters / 200))
        points = []
        
        for i in range(num_points + 1):
            ratio = i / num_points
            curve = math.sin(ratio * math.pi) * 0.0003
            
            lat = lat1 + (lat2 - lat1) * ratio + curve
            lon = lon1 + (lon2 - lon1) * ratio + curve
            points.append([lat, lon])
        
        distance = geodesic(origin, destination).meters
        return points, distance

    def _calculate_distance(self, coords: List) -> float:
        if len(coords) < 2:
            return 0
        return sum(geodesic(coords[i], coords[i + 1]).meters for i in range(len(coords) - 1))

    def format_distance(self, meters: float) -> str:
        return f"{meters:.0f} m" if meters < 1000 else f"{meters/1000:.1f} km"

    def format_duration(self, meters: float) -> str:
        mins = max(1, int((meters / 1000 / 25) * 60))
        
        if mins < 60:
            return f"{mins} phút"
        else:
            hours = mins // 60
            remaining = mins % 60
            return f"{hours} giờ {remaining} phút" if remaining else f"{hours} giờ"

class EcoOptimizer:
    VEHICLE_MODELS = {
        'VF e34': {'battery': 42, 'consumption': 7.0, 'range': 300},
        'VF 8': {'battery': 82, 'consumption': 8.2, 'range': 400},
        'VF 9': {'battery': 106, 'consumption': 9.1, 'range': 450},
        'Feliz S': {'battery': 24, 'consumption': 6.5, 'range': 200},
        'none': {'battery': 0, 'consumption': 0, 'range': 0}
    }
    
    CHARGING_STATIONS = {
        'VinFast Quận 1': (10.7757, 106.7000),
        'VinFast Quận 7': (10.7324, 106.7260),
        'VinFast Thủ Đức': (10.8494, 106.7710),
        'VinFast Gò Vấp': (10.8380, 106.6650),
        'VinFast Bình Thạnh': (10.8070, 106.7130),
    }

    @classmethod
    def calculate_energy_usage(cls, distance_km: float, vehicle_model: str) -> float:
        if vehicle_model == 'none' or vehicle_model not in cls.VEHICLE_MODELS:
            return 0
        return (distance_km * cls.VEHICLE_MODELS[vehicle_model]['consumption']) / 100

    @classmethod
    def calculate_cost_savings(cls, energy_kwh: float) -> int:
        electricity_cost = energy_kwh * 3000
        petrol_cost = (energy_kwh * 100) * 25000
        return max(0, int(petrol_cost - electricity_cost))

def create_map(origin: str, destination: str, origin_coords: Tuple[float, float], 
              destination_coords: Tuple[float, float], route_coords: List, 
              distance: float, charging_stops: List = None) -> str:
    
    center_lat = (origin_coords[0] + destination_coords[0]) / 2
    center_lng = (origin_coords[1] + destination_coords[1]) / 2
    
    m = folium.Map(
        location=[center_lat, center_lng], 
        zoom_start=13,
        tiles='OpenStreetMap',
        width='100%',
        height='500px'
    )
    
    folium.Marker(origin_coords, popup=f"🏁 {origin}", icon=folium.Icon(color='green')).add_to(m)
    folium.Marker(destination_coords, popup=f"🎯 {destination}", icon=folium.Icon(color='red')).add_to(m)
    
    folium.PolyLine(route_coords, color='blue', weight=6, opacity=0.7).add_to(m)
    
    if charging_stops:
        for stop in charging_stops:
            folium.Marker(
                stop['coords'], 
                popup=f"⚡ {stop['station']}",
                icon=folium.Icon(color='orange', icon='bolt')
            ).add_to(m)

    info_html = f"""
    <div style="position: absolute; top: 10px; left: 10px; background: white; 
               padding: 12px; border: 2px solid #007bff; border-radius: 8px; 
               font-family: Arial; max-width: 320px; z-index: 1000; box-shadow: 0 2px 6px rgba(0,0,0,0.3);">
        <b style="color: #007bff; font-size: 16px;">🚗 SMART ROUTE PLANNER</b><br>
        <hr style="margin: 8px 0;">
        <b>📍 Từ:</b> {origin}<br>
        <b>🎯 Đến:</b> {destination}<br>
        <b>📏 Khoảng cách:</b> {planner.format_distance(distance)}<br>
        <b>⏱️ Thời gian:</b> {planner.format_duration(distance)}
        {f"<br><b>⚡ Trạm sạc:</b> {len(charging_stops)} điểm" if charging_stops else ""}
    </div>
    """
    m.get_root().html.add_child(folium.Element(info_html))
    
    return m._repr_html_()

# Khởi tạo core components
smart_geocoder = SmartGeocoder()
planner = RoutePlanner()

@app.route('/')
def home():
    return render_template('index.html')

@app.route('/api/route', methods=['POST'])
def find_route():
    """API tìm đường thông minh"""
    try:
        data = request.get_json()
        origin = data.get('origin', '').strip()
        destination = data.get('destination', '').strip()
        vehicle_model = data.get('vehicle_model', 'none')
        current_battery = data.get('current_battery')
        
        if not origin or not destination:
            return jsonify({'error': 'Vui lòng nhập đầy đủ địa chỉ'})
        
        logger.info(f"🔍 Finding route: {origin} → {destination}")
        
        origin_coords = planner.get_coordinates(origin)
        destination_coords = planner.get_coordinates(destination)
        
        if not origin_coords:
            return jsonify({'error': f'Không tìm thấy địa chỉ: {origin}'})
        if not destination_coords:
            return jsonify({'error': f'Không tìm thấy địa chỉ: {destination}'})
        
        route_coords, distance = planner.find_route(origin_coords, destination_coords)
        
        # EV optimization
        charging_stops = []
        energy_used = 0
        cost_savings = 0
        
        is_ev = vehicle_model != 'none' and current_battery is not None
        if is_ev:
            current_battery_kwh = EcoOptimizer.VEHICLE_MODELS[vehicle_model]['battery'] * (current_battery / 100)
            energy_used = EcoOptimizer.calculate_energy_usage(distance/1000, vehicle_model)
            cost_savings = EcoOptimizer.calculate_cost_savings(energy_used)
        
        map_html = create_map(origin, destination, origin_coords, destination_coords, 
                             route_coords, distance, charging_stops)
        
        response = {
            'success': True,
            'map_html': map_html,
            'distance': planner.format_distance(distance),
            'duration': planner.format_duration(distance),
            'route_type': 'eco_optimized' if is_ev else 'normal'
        }
        
        if is_ev:
            response.update({
                'energy_used_kwh': round(energy_used, 2),
                'cost_savings_vnd': cost_savings,
                'charging_stops': charging_stops,
                'vehicle_model': vehicle_model,
                'current_battery': f"{current_battery}%",
                'eco_tips': [
                    "Tăng tốc từ từ, tránh đạp mạnh chân ga",
                    "Duy trì tốc độ ổn định 40-60km/h", 
                    "Tận dụng phanh tái sinh năng lượng"
                ]
            })
        
        return jsonify(response)
        
    except Exception as e:
        logger.error(f"❌ Route error: {e}")
        return jsonify({'error': 'Lỗi hệ thống. Vui lòng thử lại.'})

@app.route('/api/suggestions')
def get_suggestions():
    suggestions = [
        "Phở Hòa Pasteur", "Highlands Coffee", "Vincom Center",
        "Bệnh viện Chợ Rẫy", "Đại học Bách Khoa", "Chợ Bến Thành",
        "Quận 1", "Quận 7", "Bình Thạnh", "Thủ Đức"
    ]
    return jsonify({'suggestions': suggestions})

@app.route('/api/vehicle-models')
def get_vehicle_models():
    return jsonify({
        'models': {k: v for k, v in EcoOptimizer.VEHICLE_MODELS.items() if k != 'none'},
        'default': 'none'
    })

@app.route('/api/spell-check', methods=['POST'])
def spell_check_api():
    """API kiểm tra và sửa lỗi chính tả"""
    data = request.get_json()
    text = data.get('text', '').strip()
    
    if not text:
        return jsonify({'error': 'No text provided'})
    
    corrected = smart_geocoder.spell_checker.smart_correct(text)
    similarity = fuzz.ratio(text.lower(), corrected.lower())
    
    return jsonify({
        'original': text,
        'corrected': corrected,
        'was_corrected': text != corrected,
        'similarity_score': similarity,
        'confidence': 'high' if similarity >= 90 else 'medium' if similarity >= 70 else 'low'
    })

@app.route('/health')
def health_check():
    return jsonify({
        'status': 'healthy', 
        'service': 'Smart Route Planner v3.0',
        'version': '3.0',
        'features': ['smart-routing', 'ev-optimization', 'spell-checking', 'fuzzy-matching']
    })

if __name__ == '__main__':
    port = int(os.environ.get('PORT', 5000))
    app.run(host='0.0.0.0', port=port, debug=False)