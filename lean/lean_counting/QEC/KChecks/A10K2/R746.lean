import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2984 = true := by
  decide +kernel

theorem tot2984 : totK PA10K2 A10K2.t2984 = [0, 0, 381209049163, 1468176592801, 1897373729412, 904104020984, 149655288825, 5410721913, 0, 0] := by
  decide +kernel

theorem rows2985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2985 = true := by
  decide +kernel

theorem tot2985 : totK PA10K2 A10K2.t2985 = [0, 0, 177215217843, 1382952346993, 2214641080209, 812745489303, 64715640525, 0, 0, 0] := by
  decide +kernel

theorem rows2986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2986 = true := by
  decide +kernel

theorem tot2986 : totK PA10K2 A10K2.t2986 = [0, 0, 485243461101, 1590675248958, 1807850332402, 846646384338, 147846456327, 5546304973, 0, 0] := by
  decide +kernel

theorem rows2987 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2987 = true := by
  decide +kernel

theorem tot2987 : totK PA10K2 A10K2.t2987 = [0, 193918436879, 729916697288, 1548055819682, 1793883878119, 700659429549, 57202917555, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
