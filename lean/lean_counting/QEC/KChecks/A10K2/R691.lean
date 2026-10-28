import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2764 = true := by
  decide +kernel

theorem tot2764 : totK PA10K2 A10K2.t2764 = [295806202328, 1186041029011, 1830507475347, 1169438153426, 233437977769, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2765 = true := by
  decide +kernel

theorem tot2765 : totK PA10K2 A10K2.t2765 = [504850548399, 1888215101820, 2128304703731, 608502649037, 27587116501, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2766 = true := by
  decide +kernel

theorem tot2766 : totK PA10K2 A10K2.t2766 = [0, 557022127150, 1997175696121, 2049936853702, 490406975279, 13803657628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2767 = true := by
  decide +kernel

theorem tot2767 : totK PA10K2 A10K2.t2767 = [0, 589214384537, 1924537609949, 1827343604889, 560610888101, 49111353342, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
