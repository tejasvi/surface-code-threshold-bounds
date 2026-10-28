import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5484 = true := by
  decide +kernel

theorem tot5484 : totK PA10K2 A10K2.t5484 = [0, 0, 306484836393, 1572307906743, 2126274254396, 669955351408, 38148714322, 0, 0, 0] := by
  decide +kernel

theorem rows5485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5485 = true := by
  decide +kernel

theorem tot5485 : totK PA10K2 A10K2.t5485 = [0, 0, 212714494464, 1066059313549, 1916847365384, 1189186849943, 233528391130, 6354482628, 0, 0] := by
  decide +kernel

theorem rows5486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5486 = true := by
  decide +kernel

theorem tot5486 : totK PA10K2 A10K2.t5486 = [0, 0, 464512307610, 1754817943554, 1986619127229, 574239491576, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5487 = true := by
  decide +kernel

theorem tot5487 : totK PA10K2 A10K2.t5487 = [0, 0, 82133137866, 895552954637, 2066284343764, 1443157641333, 308421487502, 25371180993, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
