import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7936 = true := by
  decide +kernel

theorem tot7936 : totK PA10K2 A10K2.t7936 = [0, 0, 532721781654, 1879866076857, 1855626072875, 476668032415, 23598218780, 0, 0, 0] := by
  decide +kernel

theorem rows7937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7937 = true := by
  decide +kernel

theorem tot7937 : totK PA10K2 A10K2.t7937 = [0, 0, 200545299540, 1184887040167, 2104753801207, 1271354683788, 208266314314, 6904928264, 0, 0] := by
  decide +kernel

theorem rows7938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7938 = true := by
  decide +kernel

theorem tot7938 : totK PA10K2 A10K2.t7938 = [0, 0, 298479604829, 1374006320380, 2068401952871, 1029730614415, 108741400227, 0, 0, 0] := by
  decide +kernel

theorem rows7939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7939 = true := by
  decide +kernel

theorem tot7939 : totK PA10K2 A10K2.t7939 = [0, 0, 466273731196, 1777710448401, 2034326416528, 640394320181, 29938065069, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
