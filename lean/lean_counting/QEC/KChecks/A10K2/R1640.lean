import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6560 = true := by
  decide +kernel

theorem tot6560 : totK PA10K2 A10K2.t6560 = [0, 0, 460445493745, 1804920129109, 2124434531902, 680396932022, 41578252044, 0, 0, 0] := by
  decide +kernel

theorem rows6561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6561 = true := by
  decide +kernel

theorem tot6561 : totK PA10K2 A10K2.t6561 = [0, 0, 551979655817, 1965272482202, 1806321966283, 445237446955, 26479096260, 0, 0, 0] := by
  decide +kernel

theorem rows6562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6562 = true := by
  decide +kernel

theorem tot6562 : totK PA10K2 A10K2.t6562 = [0, 0, 258151593043, 1390797565828, 2233665042230, 912494003067, 69771422414, 0, 0, 0] := by
  decide +kernel

theorem rows6563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6563 = true := by
  decide +kernel

theorem tot6563 : totK PA10K2 A10K2.t6563 = [0, 0, 0, 518964181651, 1849703058990, 1773456634330, 479302778684, 31082886609, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
