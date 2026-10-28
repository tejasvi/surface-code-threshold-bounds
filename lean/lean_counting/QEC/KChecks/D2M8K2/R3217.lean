import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12868 = true := by
  decide +kernel

theorem tot12868 : totK PD2M8K2 D2M8K2.t12868 = [0, 110081403855, 352250966319, 361967450040, 82291329212, 1334241821, 0, 0] := by
  decide +kernel

theorem rows12869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12869 = true := by
  decide +kernel

theorem tot12869 : totK PD2M8K2 D2M8K2.t12869 = [0, 166506313238, 443712701706, 270700581088, 29700519454, 0, 0, 0] := by
  decide +kernel

theorem rows12870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12870 = true := by
  decide +kernel

theorem tot12870 : totK PD2M8K2 D2M8K2.t12870 = [0, 148990985574, 451526627048, 288342812087, 23068983254, 0, 0, 0] := by
  decide +kernel

theorem rows12871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12871 = true := by
  decide +kernel

theorem tot12871 : totK PD2M8K2 D2M8K2.t12871 = [0, 0, 222755047915, 495008040460, 165179843305, 4967996017, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
