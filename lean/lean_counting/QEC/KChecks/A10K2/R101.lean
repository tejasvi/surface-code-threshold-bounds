import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t404 = true := by
  decide +kernel

theorem tot404 : totK PA10K2 A10K2.t404 = [0, 424498040112, 1607182705950, 2020716719440, 807902806040, 73990919745, 0, 0, 0, 0] := by
  decide +kernel

theorem rows405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t405 = true := by
  decide +kernel

theorem tot405 : totK PA10K2 A10K2.t405 = [0, 429964921676, 1782638288936, 2009143222820, 574815806499, 34548791282, 0, 0, 0, 0] := by
  decide +kernel

theorem rows406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t406 = true := by
  decide +kernel

theorem tot406 : totK PA10K2 A10K2.t406 = [0, 0, 553746199094, 1968140126851, 1664471756954, 395834075734, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t407 = true := by
  decide +kernel

theorem tot407 : totK PA10K2 A10K2.t407 = [0, 359532124325, 1473514484333, 1914833050481, 896857388799, 150685979414, 5410721913, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
