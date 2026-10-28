import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5436 = true := by
  decide +kernel

theorem tot5436 : totK PA10K2 A10K2.t5436 = [0, 0, 0, 463885174036, 1891727837108, 1928186001964, 448652368777, 26116334861, 0, 0] := by
  decide +kernel

theorem rows5437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5437 = true := by
  decide +kernel

theorem tot5437 : totK PA10K2 A10K2.t5437 = [0, 0, 0, 598219590438, 1937796430406, 1844872455331, 458794324636, 18533161629, 0, 0] := by
  decide +kernel

theorem rows5438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5438 = true := by
  decide +kernel

theorem tot5438 : totK PA10K2 A10K2.t5438 = [0, 0, 0, 400624521330, 1764967096187, 1962224678652, 515501099505, 31889781550, 0, 0] := by
  decide +kernel

theorem rows5439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5439 = true := by
  decide +kernel

theorem tot5439 : totK PA10K2 A10K2.t5439 = [0, 0, 120678695417, 271185643134, 833221842147, 1965164285574, 1200463869940, 190799806691, 6239673734, 0] := by
  decide +kernel

end QECKChecks.A10K2
