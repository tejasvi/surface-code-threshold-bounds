import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t904 = true := by
  decide +kernel

theorem tot904 : totK PD2M8K2 D2M8K2.t904 = [0, 200026757539, 466468910187, 194195142274, 12052611869, 0, 0, 0] := by
  decide +kernel

theorem rows905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t905 = true := by
  decide +kernel

theorem tot905 : totK PD2M8K2 D2M8K2.t905 = [194038971438, 452316361775, 236137888169, 25496711798, 0, 0, 0, 0] := by
  decide +kernel

theorem rows906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t906 = true := by
  decide +kernel

theorem tot906 : totK PD2M8K2 D2M8K2.t906 = [184961365152, 453650716785, 238702340601, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t907 = true := by
  decide +kernel

theorem tot907 : totK PD2M8K2 D2M8K2.t907 = [44330716885, 343331292625, 424494592596, 78680066039, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
