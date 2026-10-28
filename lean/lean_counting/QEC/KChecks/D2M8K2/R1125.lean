import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4500 = true := by
  decide +kernel

theorem tot4500 : totK PD2M8K2 D2M8K2.t4500 = [0, 0, 0, 295392919485, 465868855405, 88079287444, 1095107716, 0] := by
  decide +kernel

theorem rows4501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4501 = true := by
  decide +kernel

theorem tot4501 : totK PD2M8K2 D2M8K2.t4501 = [0, 87687082016, 178372532519, 201196510564, 301308281207, 103055590849, 3882006667, 0] := by
  decide +kernel

theorem rows4502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4502 = true := by
  decide +kernel

theorem tot4502 : totK PD2M8K2 D2M8K2.t4502 = [0, 185570512212, 469634387307, 228333910807, 12774899742, 0, 0, 0] := by
  decide +kernel

theorem rows4503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4503 = true := by
  decide +kernel

theorem tot4503 : totK PD2M8K2 D2M8K2.t4503 = [0, 105774798199, 401738679374, 339471810117, 40209789142, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
