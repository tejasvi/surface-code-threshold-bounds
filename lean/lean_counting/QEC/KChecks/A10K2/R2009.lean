import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8036 = true := by
  decide +kernel

theorem tot8036 : totK PA10K2 A10K2.t8036 = [0, 0, 0, 303413067912, 1147450502938, 1757526020237, 1433574655672, 400209470140, 29010686974, 0] := by
  decide +kernel

theorem rows8037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8037 = true := by
  decide +kernel

theorem tot8037 : totK PA10K2 A10K2.t8037 = [0, 0, 0, 455965171665, 1815125060191, 2009570341712, 523925403284, 31662601151, 0, 0] := by
  decide +kernel

theorem rows8038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8038 = true := by
  decide +kernel

theorem tot8038 : totK PA10K2 A10K2.t8038 = [0, 0, 0, 109108466041, 1153728861151, 2437970203558, 1118112572593, 76390776393, 0, 0] := by
  decide +kernel

theorem rows8039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t8039 = true := by
  decide +kernel

theorem tot8039 : totK PA10K2 A10K2.t8039 = [0, 0, 0, 562276145770, 2027836237468, 1765140972134, 349629486846, 11776269449, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
