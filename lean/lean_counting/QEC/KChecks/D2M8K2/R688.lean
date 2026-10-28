import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2752 = true := by
  decide +kernel

theorem tot2752 : totK PD2M8K2 D2M8K2.t2752 = [0, 0, 188941144379, 462858812203, 240307686031, 18246066036, 0, 0] := by
  decide +kernel

theorem rows2753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2753 = true := by
  decide +kernel

theorem tot2753 : totK PD2M8K2 D2M8K2.t2753 = [0, 0, 203514867190, 481878827797, 190448557632, 5193265422, 0, 0] := by
  decide +kernel

theorem rows2754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2754 = true := by
  decide +kernel

theorem tot2754 : totK PD2M8K2 D2M8K2.t2754 = [0, 0, 180163922697, 474916129480, 237284341725, 12227244834, 0, 0] := by
  decide +kernel

theorem rows2755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2755 = true := by
  decide +kernel

theorem tot2755 : totK PD2M8K2 D2M8K2.t2755 = [0, 0, 180768526525, 469512372163, 231979103890, 12581014784, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
