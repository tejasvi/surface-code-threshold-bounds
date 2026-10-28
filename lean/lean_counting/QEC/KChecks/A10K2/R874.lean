import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3496 = true := by
  decide +kernel

theorem tot3496 : totK PA10K2 A10K2.t3496 = [0, 0, 0, 817833201469, 2280598661522, 1378462020711, 134357289325, 0, 0, 0] := by
  decide +kernel

theorem rows3497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3497 = true := by
  decide +kernel

theorem tot3497 : totK PA10K2 A10K2.t3497 = [0, 0, 0, 515342799999, 1885127282786, 1826093775182, 375882183278, 11740475125, 0, 0] := by
  decide +kernel

theorem rows3498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3498 = true := by
  decide +kernel

theorem tot3498 : totK PA10K2 A10K2.t3498 = [0, 0, 0, 538587171847, 1841139682224, 1858322275411, 518086290791, 32470938769, 0, 0] := by
  decide +kernel

theorem rows3499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3499 = true := by
  decide +kernel

theorem tot3499 : totK PA10K2 A10K2.t3499 = [0, 0, 0, 529476398151, 1935099682853, 1874173748655, 418949244218, 13227942247, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
