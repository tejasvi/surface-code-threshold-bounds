import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t668 = true := by
  decide +kernel

theorem tot668 : totK PA10K2 A10K2.t668 = [0, 0, 0, 526469971285, 1876107913417, 1644730373228, 407937906429, 30220878370, 0, 0] := by
  decide +kernel

theorem rows669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t669 = true := by
  decide +kernel

theorem tot669 : totK PA10K2 A10K2.t669 = [0, 0, 480042370635, 1860584637507, 1934644784276, 478491233320, 25710589949, 0, 0, 0] := by
  decide +kernel

theorem rows670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t670 = true := by
  decide +kernel

theorem tot670 : totK PA10K2 A10K2.t670 = [0, 0, 296125999636, 1546719311441, 2101222220103, 702779175943, 45092337030, 0, 0, 0] := by
  decide +kernel

theorem rows671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t671 = true := by
  decide +kernel

theorem tot671 : totK PA10K2 A10K2.t671 = [0, 0, 280701655614, 1184733102750, 1963163602472, 1099143483018, 174361211873, 5546304973, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
