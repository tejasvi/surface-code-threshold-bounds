import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4840 = true := by
  decide +kernel

theorem tot4840 : totK PA10K2 A10K2.t4840 = [0, 493592159672, 1849545560491, 1838749508890, 476153420619, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4841 = true := by
  decide +kernel

theorem tot4841 : totK PA10K2 A10K2.t4841 = [519258088118, 1689914134849, 1864603100096, 722697244420, 70541832378, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4842 = true := by
  decide +kernel

theorem tot4842 : totK PA10K2 A10K2.t4842 = [39188486879, 908458080807, 2055671387294, 1394522371108, 354636896379, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4843 = true := by
  decide +kernel

theorem tot4843 : totK PA10K2 A10K2.t4843 = [378909649737, 1278206925530, 1750630394908, 1133722619992, 196467966429, 6034215561, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
