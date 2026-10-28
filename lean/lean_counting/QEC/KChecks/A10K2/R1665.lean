import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6660 = true := by
  decide +kernel

theorem tot6660 : totK PA10K2 A10K2.t6660 = [276411238399, 1197191135269, 1942061035801, 1210531551212, 209030255814, 5460492893, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6661 = true := by
  decide +kernel

theorem tot6661 : totK PA10K2 A10K2.t6661 = [282983913787, 1465729625111, 2127605331209, 858674345912, 64965193577, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6662 = true := by
  decide +kernel

theorem tot6662 : totK PA10K2 A10K2.t6662 = [0, 470766910922, 1827531328917, 1893756934771, 519405128102, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6663 = true := by
  decide +kernel

theorem tot6663 : totK PA10K2 A10K2.t6663 = [0, 563986816664, 1952347223709, 1931312770011, 453415828782, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
