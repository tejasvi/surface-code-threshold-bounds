import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1420 = true := by
  decide +kernel

theorem tot1420 : totK PD2M8K2 D2M8K2.t1420 = [0, 0, 181605539134, 461280355488, 226150409147, 17332674355, 0, 0] := by
  decide +kernel

theorem rows1421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1421 = true := by
  decide +kernel

theorem tot1421 : totK PD2M8K2 D2M8K2.t1421 = [0, 0, 212887084122, 487513689345, 171878432382, 5235228720, 0, 0] := by
  decide +kernel

theorem rows1422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1422 = true := by
  decide +kernel

theorem tot1422 : totK PD2M8K2 D2M8K2.t1422 = [0, 0, 104673049668, 409108995927, 299751298602, 38288014434, 1166720416, 0] := by
  decide +kernel

theorem rows1423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1423 = true := by
  decide +kernel

theorem tot1423 : totK PD2M8K2 D2M8K2.t1423 = [0, 0, 40100656767, 368322972743, 418357257386, 42505695625, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
