import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1924 = true := by
  decide +kernel

theorem tot1924 : totK PA10K2 A10K2.t1924 = [0, 0, 478142931709, 1548790971505, 1616068749397, 863716460446, 360456782390, 43132710386, 0, 0] := by
  decide +kernel

theorem rows1925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1925 = true := by
  decide +kernel

theorem tot1925 : totK PA10K2 A10K2.t1925 = [0, 0, 368716511760, 1668956504942, 2126309029965, 731585879253, 47308813573, 0, 0, 0] := by
  decide +kernel

theorem rows1926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1926 = true := by
  decide +kernel

theorem tot1926 : totK PA10K2 A10K2.t1926 = [0, 0, 0, 445015917037, 1760174021399, 1897022061725, 512607428168, 31768748853, 0, 0] := by
  decide +kernel

theorem rows1927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1927 = true := by
  decide +kernel

theorem tot1927 : totK PA10K2 A10K2.t1927 = [0, 0, 403059149735, 1560149338054, 2036470846873, 884855736519, 82317275805, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
