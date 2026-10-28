import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8924 = true := by
  decide +kernel

theorem tot8924 : totK PD2M8K2 D2M8K2.t8924 = [165665948659, 450142072402, 277493764580, 26828975774, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8925 = true := by
  decide +kernel

theorem tot8925 : totK PD2M8K2 D2M8K2.t8925 = [92620862180, 389275375591, 361933488931, 60211187644, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows8926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8926 = true := by
  decide +kernel

theorem tot8926 : totK PD2M8K2 D2M8K2.t8926 = [0, 244795579500, 494311850760, 150956026147, 3526328257, 0, 0, 0] := by
  decide +kernel

theorem rows8927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8927 = true := by
  decide +kernel

theorem tot8927 : totK PD2M8K2 D2M8K2.t8927 = [0, 182313016982, 463854770265, 221928968376, 17064405924, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
