import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5956 = true := by
  decide +kernel

theorem tot5956 : totK PA10K2 A10K2.t5956 = [0, 0, 0, 888020120321, 2282429410473, 1110727264642, 97111396872, 0, 0, 0] := by
  decide +kernel

theorem rows5957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5957 = true := by
  decide +kernel

theorem tot5957 : totK PA10K2 A10K2.t5957 = [0, 0, 663562021630, 1935233717358, 1672995922730, 567855720579, 114566238167, 5528811039, 0, 0] := by
  decide +kernel

theorem rows5958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5958 = true := by
  decide +kernel

theorem tot5958 : totK PA10K2 A10K2.t5958 = [0, 308060813752, 1186716902123, 1784228744822, 1282878857188, 377234041529, 29010686974, 0, 0, 0] := by
  decide +kernel

theorem rows5959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5959 = true := by
  decide +kernel

theorem tot5959 : totK PA10K2 A10K2.t5959 = [0, 487172143456, 1817458622035, 1995125215051, 565768320652, 19022894715, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
