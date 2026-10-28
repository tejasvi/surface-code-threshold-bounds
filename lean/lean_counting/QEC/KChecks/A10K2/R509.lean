import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2036 = true := by
  decide +kernel

theorem tot2036 : totK PA10K2 A10K2.t2036 = [475019784619, 1639823469985, 1872101741127, 851919522133, 174481072788, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2037 = true := by
  decide +kernel

theorem tot2037 : totK PA10K2 A10K2.t2037 = [310203719009, 1425227745476, 2119456894498, 1083740113135, 125126879346, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2038 = true := by
  decide +kernel

theorem tot2038 : totK PA10K2 A10K2.t2038 = [0, 609641037450, 2084194371787, 1904487847491, 410936314915, 12504782964, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2039 = true := by
  decide +kernel

theorem tot2039 : totK PA10K2 A10K2.t2039 = [0, 373073674782, 1559885259536, 2031672156772, 836255558646, 75408522201, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
