import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7792 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7792 = true := by
  decide +kernel

theorem tot7792 : totK PA10K2 A10K2.t7792 = [0, 0, 469687875743, 1724782377125, 2028235099976, 716380562223, 56143165367, 0, 0, 0] := by
  decide +kernel

theorem rows7793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7793 = true := by
  decide +kernel

theorem tot7793 : totK PA10K2 A10K2.t7793 = [0, 0, 519736080671, 1907695370067, 1867375560010, 496270332510, 31080743953, 0, 0, 0] := by
  decide +kernel

theorem rows7794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7794 = true := by
  decide +kernel

theorem tot7794 : totK PA10K2 A10K2.t7794 = [0, 0, 118285025063, 969331984385, 2139390608246, 1449964233641, 251898953485, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7795 = true := by
  decide +kernel

theorem tot7795 : totK PA10K2 A10K2.t7795 = [0, 0, 283437181451, 1381653533726, 2136683964944, 1027765753483, 103029487249, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
