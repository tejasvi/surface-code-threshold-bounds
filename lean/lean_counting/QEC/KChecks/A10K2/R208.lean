import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t832 = true := by
  decide +kernel

theorem tot832 : totK PA10K2 A10K2.t832 = [0, 293192342777, 1362339813393, 2015318191336, 1073181686382, 178885000820, 6034215561, 0, 0, 0] := by
  decide +kernel

theorem rows833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t833 = true := by
  decide +kernel

theorem tot833 : totK PA10K2 A10K2.t833 = [0, 269012435216, 1430841093745, 2151614582733, 890948171735, 60138905232, 0, 0, 0, 0] := by
  decide +kernel

theorem rows834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t834 = true := by
  decide +kernel

theorem tot834 : totK PA10K2 A10K2.t834 = [0, 486939703310, 1627130254465, 1832410376902, 868294441615, 149739032125, 6239673734, 0, 0, 0] := by
  decide +kernel

theorem rows835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t835 = true := by
  decide +kernel

theorem tot835 : totK PA10K2 A10K2.t835 = [0, 313255680567, 1484236971267, 2206691725596, 920073082559, 76899999747, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
