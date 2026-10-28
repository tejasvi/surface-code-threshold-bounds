import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2012 = true := by
  decide +kernel

theorem tot2012 : totK PA10K2 A10K2.t2012 = [0, 0, 0, 606986079230, 2027282178805, 1923939134142, 446161927764, 12199886344, 0, 0] := by
  decide +kernel

theorem rows2013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2013 = true := by
  decide +kernel

theorem tot2013 : totK PA10K2 A10K2.t2013 = [0, 0, 409909650706, 1356280555513, 1560079787734, 1015729895246, 461574447858, 50432252117, 0, 0] := by
  decide +kernel

theorem rows2014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2014 = true := by
  decide +kernel

theorem tot2014 : totK PA10K2 A10K2.t2014 = [0, 0, 344646309828, 1631294530061, 2127850626776, 836316009710, 71733655854, 0, 0, 0] := by
  decide +kernel

theorem rows2015 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2015 = true := by
  decide +kernel

theorem tot2015 : totK PA10K2 A10K2.t2015 = [0, 0, 27988993771, 587848946758, 2020148300728, 1825236951991, 387931015844, 11991740650, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
