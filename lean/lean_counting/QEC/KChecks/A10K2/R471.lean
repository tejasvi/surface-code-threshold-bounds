import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1884 = true := by
  decide +kernel

theorem tot1884 : totK PA10K2 A10K2.t1884 = [0, 0, 237242196814, 1084043301586, 1937717408130, 1200728700205, 176023470860, 6354482628, 0, 0] := by
  decide +kernel

theorem rows1885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1885 = true := by
  decide +kernel

theorem tot1885 : totK PA10K2 A10K2.t1885 = [0, 0, 564107542063, 1935596748266, 1904857384825, 521345738556, 31301336365, 0, 0, 0] := by
  decide +kernel

theorem rows1886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1886 = true := by
  decide +kernel

theorem tot1886 : totK PA10K2 A10K2.t1886 = [0, 0, 0, 767785600337, 2121972712889, 1623197631433, 376427078325, 25313348169, 0, 0] := by
  decide +kernel

theorem rows1887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1887 = true := by
  decide +kernel

theorem tot1887 : totK PA10K2 A10K2.t1887 = [0, 0, 254308263408, 1347297886015, 2215383529170, 1041569325060, 99848255417, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
