import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4952 = true := by
  decide +kernel

theorem tot4952 : totK PA10K2 A10K2.t4952 = [0, 447221393346, 1674765066170, 1929101617545, 644643058622, 51475380808, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4953 = true := by
  decide +kernel

theorem tot4953 : totK PA10K2 A10K2.t4953 = [0, 135988547912, 1284542546892, 2293351228052, 964309127961, 66575634117, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4954 = true := by
  decide +kernel

theorem tot4954 : totK PA10K2 A10K2.t4954 = [0, 0, 536712811583, 1933480438742, 1751730720399, 370006161043, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4955 = true := by
  decide +kernel

theorem tot4955 : totK PA10K2 A10K2.t4955 = [0, 0, 585035497024, 1999878716390, 1798786299023, 375056890542, 21325559729, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
