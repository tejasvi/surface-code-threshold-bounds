import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4572 = true := by
  decide +kernel

theorem tot4572 : totK PA10K2 A10K2.t4572 = [0, 402954068815, 1337716912142, 1812201838012, 1014536803008, 194764897090, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows4573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4573 = true := by
  decide +kernel

theorem tot4573 : totK PA10K2 A10K2.t4573 = [0, 433289286045, 1744605406118, 1959995241588, 642169383721, 41977780483, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4574 = true := by
  decide +kernel

theorem tot4574 : totK PA10K2 A10K2.t4574 = [0, 0, 567449712104, 1993148006120, 1776575895550, 410926745669, 25734533292, 0, 0, 0] := by
  decide +kernel

theorem rows4575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4575 = true := by
  decide +kernel

theorem tot4575 : totK PA10K2 A10K2.t4575 = [0, 400965813043, 1425583149013, 1747085009907, 964358003388, 170272045458, 5718040558, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
