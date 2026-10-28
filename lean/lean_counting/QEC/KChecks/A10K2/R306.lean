import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1224 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1224 = true := by
  decide +kernel

theorem tot1224 : totK PA10K2 A10K2.t1224 = [0, 436628438835, 1640618427505, 1899448032232, 640165830958, 52230035883, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1225 = true := by
  decide +kernel

theorem tot1225 : totK PA10K2 A10K2.t1225 = [0, 110196786130, 1198494599992, 2267402637405, 1048185810871, 86881185354, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1226 = true := by
  decide +kernel

theorem tot1226 : totK PA10K2 A10K2.t1226 = [0, 322474191720, 1251740024002, 1899730397331, 1123179119563, 214224422006, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows1227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1227 = true := by
  decide +kernel

theorem tot1227 : totK PA10K2 A10K2.t1227 = [0, 252379399726, 1360575153430, 2168982657033, 1167351648243, 126746088384, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
