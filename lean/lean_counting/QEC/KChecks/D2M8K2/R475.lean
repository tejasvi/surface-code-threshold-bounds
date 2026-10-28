import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1900 = true := by
  decide +kernel

theorem tot1900 : totK PD2M8K2 D2M8K2.t1900 = [0, 0, 209322937855, 475286492352, 200643452466, 7651299259, 0, 0] := by
  decide +kernel

theorem rows1901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1901 = true := by
  decide +kernel

theorem tot1901 : totK PD2M8K2 D2M8K2.t1901 = [0, 0, 188032995930, 500272161134, 200573385159, 3843840038, 0, 0] := by
  decide +kernel

theorem rows1902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1902 = true := by
  decide +kernel

theorem tot1902 : totK PD2M8K2 D2M8K2.t1902 = [0, 0, 172028636746, 471121462156, 221813846242, 12574356851, 0, 0] := by
  decide +kernel

theorem rows1903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1903 = true := by
  decide +kernel

theorem tot1903 : totK PD2M8K2 D2M8K2.t1903 = [0, 0, 184387000663, 450463521116, 235144169062, 18063184643, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
