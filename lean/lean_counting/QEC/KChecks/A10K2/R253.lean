import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1012 = true := by
  decide +kernel

theorem tot1012 : totK PA10K2 A10K2.t1012 = [0, 0, 711864872221, 2227235897334, 1847141356222, 343106818255, 6574379264, 0, 0, 0] := by
  decide +kernel

theorem rows1013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1013 = true := by
  decide +kernel

theorem tot1013 : totK PA10K2 A10K2.t1013 = [0, 0, 523271164560, 1790935244483, 1927144720460, 673658525539, 56070559746, 0, 0, 0] := by
  decide +kernel

theorem rows1014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1014 = true := by
  decide +kernel

theorem tot1014 : totK PA10K2 A10K2.t1014 = [0, 0, 452115777036, 1784181564414, 1949210135120, 541521652496, 32523532663, 0, 0, 0] := by
  decide +kernel

theorem rows1015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1015 = true := by
  decide +kernel

theorem tot1015 : totK PA10K2 A10K2.t1015 = [0, 0, 183504757507, 1149619645059, 2104613429185, 1232736814187, 248708063226, 20331139758, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
