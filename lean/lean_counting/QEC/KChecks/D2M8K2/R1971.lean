import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7884 = true := by
  decide +kernel

theorem tot7884 : totK PD2M8K2 D2M8K2.t7884 = [0, 0, 288560502050, 512190598402, 91161924725, 1369150432, 0, 0] := by
  decide +kernel

theorem rows7885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7885 = true := by
  decide +kernel

theorem tot7885 : totK PD2M8K2 D2M8K2.t7885 = [0, 165681710033, 432706124494, 288251913221, 34470929855, 0, 0, 0] := by
  decide +kernel

theorem rows7886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7886 = true := by
  decide +kernel

theorem tot7886 : totK PD2M8K2 D2M8K2.t7886 = [0, 190670099117, 481087396610, 228795061121, 12432084775, 0, 0, 0] := by
  decide +kernel

theorem rows7887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7887 = true := by
  decide +kernel

theorem tot7887 : totK PD2M8K2 D2M8K2.t7887 = [0, 43096145850, 295025833887, 421276061215, 151907265547, 9977052014, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
