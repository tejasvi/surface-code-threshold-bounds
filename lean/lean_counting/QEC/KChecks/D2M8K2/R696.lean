import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2784 = true := by
  decide +kernel

theorem tot2784 : totK PD2M8K2 D2M8K2.t2784 = [0, 0, 157041425744, 432755760730, 276892829159, 26192173054, 0, 0] := by
  decide +kernel

theorem rows2785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2785 = true := by
  decide +kernel

theorem tot2785 : totK PD2M8K2 D2M8K2.t2785 = [0, 0, 87780774384, 420320072115, 360820455812, 29077717679, 0, 0] := by
  decide +kernel

theorem rows2786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2786 = true := by
  decide +kernel

theorem tot2786 : totK PD2M8K2 D2M8K2.t2786 = [0, 0, 75209244945, 317539102137, 398577414987, 81003779022, 1323630408, 0] := by
  decide +kernel

theorem rows2787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2787 = true := by
  decide +kernel

theorem tot2787 : totK PD2M8K2 D2M8K2.t2787 = [0, 0, 178225730332, 451371275413, 253494890137, 21888561396, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
