import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1928 = true := by
  decide +kernel

theorem tot1928 : totK PA10K2 A10K2.t1928 = [0, 0, 159145628258, 1300950968385, 2304593610594, 934526171475, 66114292304, 0, 0, 0] := by
  decide +kernel

theorem rows1929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1929 = true := by
  decide +kernel

theorem tot1929 : totK PA10K2 A10K2.t1929 = [0, 0, 486939703310, 1635474020560, 1828041675018, 888296441723, 158171802017, 6239673734, 0, 0] := by
  decide +kernel

theorem rows1930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1930 = true := by
  decide +kernel

theorem tot1930 : totK PA10K2 A10K2.t1930 = [0, 0, 313255680567, 1481981708558, 2224295183836, 966752149767, 75584115993, 0, 0, 0] := by
  decide +kernel

theorem rows1931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1931 = true := by
  decide +kernel

theorem tot1931 : totK PA10K2 A10K2.t1931 = [0, 0, 0, 608806226317, 2147571928971, 1938178629496, 370497732569, 6962742351, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
