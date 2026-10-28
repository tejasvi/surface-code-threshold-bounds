import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6688 = true := by
  decide +kernel

theorem tot6688 : totK PD2M8K2 D2M8K2.t6688 = [0, 3756869540, 194906335374, 472692547580, 194485516540, 11991925116, 0, 0] := by
  decide +kernel

theorem rows6689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6689 = true := by
  decide +kernel

theorem tot6689 : totK PD2M8K2 D2M8K2.t6689 = [0, 183063352062, 445540394311, 242918824689, 22633514653, 0, 0, 0] := by
  decide +kernel

theorem rows6690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6690 = true := by
  decide +kernel

theorem tot6690 : totK PD2M8K2 D2M8K2.t6690 = [0, 197294089122, 459431555831, 228304239180, 16988898864, 0, 0, 0] := by
  decide +kernel

theorem rows6691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6691 = true := by
  decide +kernel

theorem tot6691 : totK PD2M8K2 D2M8K2.t6691 = [0, 37670822061, 337128264275, 428894145903, 80246914168, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
