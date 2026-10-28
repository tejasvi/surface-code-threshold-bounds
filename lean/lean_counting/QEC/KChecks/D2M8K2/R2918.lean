import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11672 = true := by
  decide +kernel

theorem tot11672 : totK PD2M8K2 D2M8K2.t11672 = [49717183811, 278443582559, 380880034634, 182066344126, 21385708972, 0, 0, 0] := by
  decide +kernel

theorem rows11673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11673 = true := by
  decide +kernel

theorem tot11673 : totK PD2M8K2 D2M8K2.t11673 = [0, 203724087529, 482399428839, 205799629453, 7994456143, 0, 0, 0] := by
  decide +kernel

theorem rows11674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11674 = true := by
  decide +kernel

theorem tot11674 : totK PD2M8K2 D2M8K2.t11674 = [84808482832, 272055670260, 358819199842, 168887435774, 8036788501, 0, 0, 0] := by
  decide +kernel

theorem rows11675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11675 = true := by
  decide +kernel

theorem tot11675 : totK PD2M8K2 D2M8K2.t11675 = [180556317488, 459682437360, 258312920454, 24101534790, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
