import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7988 = true := by
  decide +kernel

theorem tot7988 : totK PD2M8K2 D2M8K2.t7988 = [0, 0, 38603867747, 352071497601, 457458693503, 47101232994, 0, 0] := by
  decide +kernel

theorem rows7989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7989 = true := by
  decide +kernel

theorem tot7989 : totK PD2M8K2 D2M8K2.t7989 = [0, 0, 175063465396, 441842276925, 275950043794, 27368242988, 0, 0] := by
  decide +kernel

theorem rows7990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7990 = true := by
  decide +kernel

theorem tot7990 : totK PD2M8K2 D2M8K2.t7990 = [0, 0, 197678044991, 493292053380, 215011828945, 7306724290, 0, 0] := by
  decide +kernel

theorem rows7991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7991 = true := by
  decide +kernel

theorem tot7991 : totK PD2M8K2 D2M8K2.t7991 = [0, 0, 0, 211204408971, 476126708337, 204555554204, 13604428459, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
