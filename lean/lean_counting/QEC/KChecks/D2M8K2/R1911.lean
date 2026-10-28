import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7644 = true := by
  decide +kernel

theorem tot7644 : totK PD2M8K2 D2M8K2.t7644 = [0, 0, 124411509241, 415210038907, 313287733430, 33989773318, 0, 0] := by
  decide +kernel

theorem rows7645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7645 = true := by
  decide +kernel

theorem tot7645 : totK PD2M8K2 D2M8K2.t7645 = [0, 0, 185277095551, 453844108123, 251973564272, 22242851466, 0, 0] := by
  decide +kernel

theorem rows7646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7646 = true := by
  decide +kernel

theorem tot7646 : totK PD2M8K2 D2M8K2.t7646 = [0, 0, 187299572678, 481342833234, 225971635585, 14882113416, 0, 0] := by
  decide +kernel

theorem rows7647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7647 = true := by
  decide +kernel

theorem tot7647 : totK PD2M8K2 D2M8K2.t7647 = [0, 0, 171257418686, 443096610377, 268855135035, 24843334852, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
