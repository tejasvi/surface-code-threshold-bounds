import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10856 = true := by
  decide +kernel

theorem tot10856 : totK PD2M8K2 D2M8K2.t10856 = [0, 0, 153087167813, 468317744198, 246787823072, 12518842064, 0, 0] := by
  decide +kernel

theorem rows10857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10857 = true := by
  decide +kernel

theorem tot10857 : totK PD2M8K2 D2M8K2.t10857 = [0, 0, 0, 293667730685, 480026956089, 70441197112, 1206465782, 0] := by
  decide +kernel

theorem rows10858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10858 = true := by
  decide +kernel

theorem tot10858 : totK PD2M8K2 D2M8K2.t10858 = [0, 0, 180347303776, 446840094852, 266923924465, 29760404672, 0, 0] := by
  decide +kernel

theorem rows10859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10859 = true := by
  decide +kernel

theorem tot10859 : totK PD2M8K2 D2M8K2.t10859 = [0, 0, 175739184896, 485298543526, 243600747251, 11487692263, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
