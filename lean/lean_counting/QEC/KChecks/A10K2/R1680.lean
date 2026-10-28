import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6720 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6720 = true := by
  decide +kernel

theorem tot6720 : totK PA10K2 A10K2.t6720 = [0, 590951554036, 2032456620582, 1988167259449, 482743344674, 13803479176, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6721 = true := by
  decide +kernel

theorem tot6721 : totK PA10K2 A10K2.t6721 = [0, 519928946027, 1870228184663, 1960134496374, 618933809961, 49107817395, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6722 = true := by
  decide +kernel

theorem tot6722 : totK PA10K2 A10K2.t6722 = [0, 528683678470, 1826608475809, 1801695920355, 483004224014, 32523532663, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6723 = true := by
  decide +kernel

theorem tot6723 : totK PA10K2 A10K2.t6723 = [0, 0, 677857632846, 2078667285866, 1616482508840, 376838222154, 25565504801, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
