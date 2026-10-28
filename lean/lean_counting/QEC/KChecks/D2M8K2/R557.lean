import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2228 = true := by
  decide +kernel

theorem tot2228 : totK PD2M8K2 D2M8K2.t2228 = [0, 0, 0, 211481293001, 453913152956, 176287170154, 11934365838, 0] := by
  decide +kernel

theorem rows2229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2229 = true := by
  decide +kernel

theorem tot2229 : totK PD2M8K2 D2M8K2.t2229 = [0, 0, 199340965798, 470714689015, 198877485948, 11071105621, 0, 0] := by
  decide +kernel

theorem rows2230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2230 = true := by
  decide +kernel

theorem tot2230 : totK PD2M8K2 D2M8K2.t2230 = [0, 0, 197398296989, 473119619088, 210543402740, 12096313584, 0, 0] := by
  decide +kernel

theorem rows2231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2231 = true := by
  decide +kernel

theorem tot2231 : totK PD2M8K2 D2M8K2.t2231 = [0, 0, 19168591844, 345251128291, 418728663650, 64857293104, 1053411165, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
