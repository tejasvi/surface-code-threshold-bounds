import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5852 = true := by
  decide +kernel

theorem tot5852 : totK PA10K2 A10K2.t5852 = [0, 0, 468642839883, 1849653038870, 1933109085820, 504626044073, 26521581199, 0, 0, 0] := by
  decide +kernel

theorem rows5853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5853 = true := by
  decide +kernel

theorem tot5853 : totK PA10K2 A10K2.t5853 = [0, 0, 0, 816951844589, 2346626728341, 1426904042557, 148856532434, 0, 0, 0] := by
  decide +kernel

theorem rows5854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5854 = true := by
  decide +kernel

theorem tot5854 : totK PA10K2 A10K2.t5854 = [0, 0, 461607179050, 1614918105878, 1777655386268, 823140346843, 173463444802, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5855 = true := by
  decide +kernel

theorem tot5855 : totK PA10K2 A10K2.t5855 = [0, 0, 0, 639536433805, 2125770832384, 1758774074671, 330827909596, 22165507785, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
