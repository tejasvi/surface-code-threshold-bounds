import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2444 = true := by
  decide +kernel

theorem tot2444 : totK PA10K2 A10K2.t2444 = [0, 591559473383, 1798414344162, 1688237331329, 705885812152, 141538455291, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows2445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2445 = true := by
  decide +kernel

theorem tot2445 : totK PA10K2 A10K2.t2445 = [342125450654, 1165893456856, 1578818751026, 1288704528337, 543147146043, 50426309422, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2446 = true := by
  decide +kernel

theorem tot2446 : totK PA10K2 A10K2.t2446 = [410979354435, 1742658104067, 2037573146200, 663980041870, 44372059190, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2447 = true := by
  decide +kernel

theorem tot2447 : totK PA10K2 A10K2.t2447 = [0, 462656009936, 1848731225198, 1874408507781, 440623685395, 25371180993, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
