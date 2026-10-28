import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t852 = true := by
  decide +kernel

theorem tot852 : totK PD2M8K2 D2M8K2.t852 = [0, 88579900808, 339415631289, 358577788609, 84425847363, 3462014130, 0, 0] := by
  decide +kernel

theorem rows853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t853 = true := by
  decide +kernel

theorem tot853 : totK PD2M8K2 D2M8K2.t853 = [0, 170642789858, 438362548862, 272090510517, 28137115437, 0, 0, 0] := by
  decide +kernel

theorem rows854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t854 = true := by
  decide +kernel

theorem tot854 : totK PD2M8K2 D2M8K2.t854 = [0, 160154851216, 457852868217, 264469619953, 16773168714, 0, 0, 0] := by
  decide +kernel

theorem rows855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t855 = true := by
  decide +kernel

theorem tot855 : totK PD2M8K2 D2M8K2.t855 = [0, 0, 229157989901, 490594060775, 159297343356, 5768874209, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
