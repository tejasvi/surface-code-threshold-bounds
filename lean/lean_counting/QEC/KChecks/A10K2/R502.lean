import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2008 = true := by
  decide +kernel

theorem tot2008 : totK PA10K2 A10K2.t2008 = [0, 0, 0, 432487417319, 1736005299079, 2145139570730, 740966385479, 56084282801, 0, 0] := by
  decide +kernel

theorem rows2009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2009 = true := by
  decide +kernel

theorem tot2009 : totK PA10K2 A10K2.t2009 = [0, 0, 0, 633901126097, 2068075695111, 1842040564396, 403548561010, 13604820459, 0, 0] := by
  decide +kernel

theorem rows2010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2010 = true := by
  decide +kernel

theorem tot2010 : totK PA10K2 A10K2.t2010 = [0, 0, 0, 115836153831, 1012559619510, 2192239020949, 1378496897680, 211796865918, 7151180950, 0] := by
  decide +kernel

theorem rows2011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2011 = true := by
  decide +kernel

theorem tot2011 : totK PA10K2 A10K2.t2011 = [0, 0, 0, 483489196292, 1802485181510, 2087852254067, 651220839525, 42304983742, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
