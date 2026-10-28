import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows92 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t92 = true := by
  decide +kernel

theorem tot92 : totK PA10K2 A10K2.t92 = [0, 295157913241, 1224250741417, 1928314923185, 1088230876025, 174361211873, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows93 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t93 = true := by
  decide +kernel

theorem tot93 : totK PA10K2 A10K2.t93 = [252426414085, 908974121474, 1585943690059, 1657017217783, 622494551489, 54843496555, 0, 0, 0, 0] := by
  decide +kernel

theorem rows94 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t94 = true := by
  decide +kernel

theorem tot94 : totK PA10K2 A10K2.t94 = [310245750236, 1569539129555, 2140489115540, 764595214953, 54149635648, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows95 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t95 = true := by
  decide +kernel

theorem tot95 : totK PA10K2 A10K2.t95 = [101820471582, 571011768864, 1718288517685, 1842559550170, 503882483649, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
