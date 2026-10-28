import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14924 = true := by
  decide +kernel

theorem tot14924 : totK PD2M8K2 D2M8K2.t14924 = [0, 195124343889, 475360236854, 199254758148, 9780024374, 0, 0, 0] := by
  decide +kernel

theorem rows14925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14925 = true := by
  decide +kernel

theorem tot14925 : totK PD2M8K2 D2M8K2.t14925 = [0, 71179355405, 351358410348, 371677764846, 66355537343, 1096505104, 0, 0] := by
  decide +kernel

theorem rows14926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14926 = true := by
  decide +kernel

theorem tot14926 : totK PD2M8K2 D2M8K2.t14926 = [0, 87932767747, 372134057080, 389057984951, 44281847926, 0, 0, 0] := by
  decide +kernel

theorem rows14927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14927 = true := by
  decide +kernel

theorem tot14927 : totK PD2M8K2 D2M8K2.t14927 = [0, 160539553595, 456186315863, 261908690412, 24541240179, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
