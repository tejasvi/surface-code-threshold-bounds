import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t780 = true := by
  decide +kernel

theorem tot780 : totK PA10K2 A10K2.t780 = [0, 307513935741, 1160567585829, 1778324516033, 1322856189524, 377361247270, 29010686974, 0, 0, 0] := by
  decide +kernel

theorem rows781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t781 = true := by
  decide +kernel

theorem tot781 : totK PA10K2 A10K2.t781 = [0, 486142690369, 1843469210151, 2050629910514, 591136551669, 19022894715, 0, 0, 0, 0] := by
  decide +kernel

theorem rows782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t782 = true := by
  decide +kernel

theorem tot782 : totK PA10K2 A10K2.t782 = [0, 0, 571150736105, 1971874102762, 1763053377833, 417990963357, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t783 = true := by
  decide +kernel

theorem tot783 : totK PA10K2 A10K2.t783 = [0, 394588770600, 1467329540883, 1910504931356, 948697540516, 159229757572, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
