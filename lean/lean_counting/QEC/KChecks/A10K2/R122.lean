import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t488 = true := by
  decide +kernel

theorem tot488 : totK PA10K2 A10K2.t488 = [75875893804, 589846071969, 1741581063896, 1851342714751, 507050671991, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t489 = true := by
  decide +kernel

theorem tot489 : totK PA10K2 A10K2.t489 = [438784493014, 1684504943558, 1927434710582, 614596769479, 46328355238, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t490 = true := by
  decide +kernel

theorem tot490 : totK PA10K2 A10K2.t490 = [304062355366, 1513058265658, 2057586993093, 781551370614, 61323581642, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t491 = true := by
  decide +kernel

theorem tot491 : totK PA10K2 A10K2.t491 = [0, 716066483315, 2158234227913, 1549934792704, 253871439097, 6354482628, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
