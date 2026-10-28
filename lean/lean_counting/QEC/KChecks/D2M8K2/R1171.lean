import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4684 = true := by
  decide +kernel

theorem tot4684 : totK PD2M8K2 D2M8K2.t4684 = [0, 0, 218689667591, 488137243813, 179363299518, 9054182512, 0, 0] := by
  decide +kernel

theorem rows4685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4685 = true := by
  decide +kernel

theorem tot4685 : totK PD2M8K2 D2M8K2.t4685 = [0, 161066439721, 444305744826, 285214525577, 36984958459, 0, 0, 0] := by
  decide +kernel

theorem rows4686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4686 = true := by
  decide +kernel

theorem tot4686 : totK PD2M8K2 D2M8K2.t4686 = [0, 178297711870, 466966193151, 244215531591, 15534827846, 0, 0, 0] := by
  decide +kernel

theorem rows4687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4687 = true := by
  decide +kernel

theorem tot4687 : totK PD2M8K2 D2M8K2.t4687 = [0, 87521967088, 342180409888, 383300811566, 85424896294, 1197396724, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
