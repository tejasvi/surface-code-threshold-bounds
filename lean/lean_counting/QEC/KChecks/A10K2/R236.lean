import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t944 = true := by
  decide +kernel

theorem tot944 : totK PA10K2 A10K2.t944 = [0, 357966842975, 1659883780085, 2189949351082, 811991906573, 62150037076, 0, 0, 0, 0] := by
  decide +kernel

theorem rows945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t945 = true := by
  decide +kernel

theorem tot945 : totK PA10K2 A10K2.t945 = [0, 0, 564299999328, 2020133694337, 2008086802338, 450435326164, 13532411735, 0, 0, 0] := by
  decide +kernel

theorem rows946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t946 = true := by
  decide +kernel

theorem tot946 : totK PA10K2 A10K2.t946 = [0, 0, 437147006990, 1683147615772, 2005415653678, 745063311549, 69386975165, 0, 0, 0] := by
  decide +kernel

theorem rows947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t947 = true := by
  decide +kernel

theorem tot947 : totK PA10K2 A10K2.t947 = [0, 0, 539359403661, 1923607689039, 1897688927833, 413605070210, 10946789654, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
