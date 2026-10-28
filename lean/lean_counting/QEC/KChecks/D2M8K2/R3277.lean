import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13108 = true := by
  decide +kernel

theorem tot13108 : totK PD2M8K2 D2M8K2.t13108 = [0, 0, 190351573767, 467145883411, 241436903922, 22865070815, 0, 0] := by
  decide +kernel

theorem rows13109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13109 = true := by
  decide +kernel

theorem tot13109 : totK PD2M8K2 D2M8K2.t13109 = [0, 0, 185291756317, 472615039984, 222655981967, 12423391470, 0, 0] := by
  decide +kernel

theorem rows13110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13110 = true := by
  decide +kernel

theorem tot13110 : totK PD2M8K2 D2M8K2.t13110 = [0, 0, 23385616275, 383101506203, 444378052028, 53623363010, 0, 0] := by
  decide +kernel

theorem rows13111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13111 = true := by
  decide +kernel

theorem tot13111 : totK PD2M8K2 D2M8K2.t13111 = [0, 0, 52338964816, 239722073152, 428968409575, 149402465258, 5218872685, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
