import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3952 = true := by
  decide +kernel

theorem tot3952 : totK PA10K2 A10K2.t3952 = [0, 0, 558493755860, 1942886761537, 1872231804483, 497338754877, 31747192500, 0, 0, 0] := by
  decide +kernel

theorem rows3953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3953 = true := by
  decide +kernel

theorem tot3953 : totK PA10K2 A10K2.t3953 = [0, 534680748697, 1840740237175, 1877109129324, 632157899383, 60209760280, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3954 = true := by
  decide +kernel

theorem tot3954 : totK PA10K2 A10K2.t3954 = [0, 327742824672, 1523235238874, 2145780711007, 882822504514, 77069730242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3955 = true := by
  decide +kernel

theorem tot3955 : totK PA10K2 A10K2.t3955 = [0, 0, 558219332543, 1985293178183, 1957442753711, 463810568886, 13816090359, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
