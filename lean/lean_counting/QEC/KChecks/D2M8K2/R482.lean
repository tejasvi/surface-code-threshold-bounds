import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1928 = true := by
  decide +kernel

theorem tot1928 : totK PD2M8K2 D2M8K2.t1928 = [0, 0, 48067303002, 327093204979, 424029382779, 78585691137, 1310285577, 0] := by
  decide +kernel

theorem rows1929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1929 = true := by
  decide +kernel

theorem tot1929 : totK PD2M8K2 D2M8K2.t1929 = [0, 0, 91091121230, 399741312125, 376623449680, 34928269318, 0, 0] := by
  decide +kernel

theorem rows1930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1930 = true := by
  decide +kernel

theorem tot1930 : totK PD2M8K2 D2M8K2.t1930 = [0, 0, 153127617070, 441955153135, 283189834922, 26995563449, 0, 0] := by
  decide +kernel

theorem rows1931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1931 = true := by
  decide +kernel

theorem tot1931 : totK PD2M8K2 D2M8K2.t1931 = [0, 0, 193304210561, 463777984424, 236486783442, 17877368512, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
