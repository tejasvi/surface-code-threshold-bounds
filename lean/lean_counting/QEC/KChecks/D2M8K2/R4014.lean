import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16056 = true := by
  decide +kernel

theorem tot16056 : totK PD2M8K2 D2M8K2.t16056 = [0, 0, 0, 214214957275, 494961090697, 168853385620, 4901932702, 0] := by
  decide +kernel

theorem rows16057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16057 = true := by
  decide +kernel

theorem tot16057 : totK PD2M8K2 D2M8K2.t16057 = [0, 33390828244, 34931502242, 165313785373, 426585860024, 218513375055, 17080783126, 0] := by
  decide +kernel

theorem rows16058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16058 = true := by
  decide +kernel

theorem tot16058 : totK PD2M8K2 D2M8K2.t16058 = [0, 197176195356, 488666263551, 210838938177, 9852138406, 0, 0, 0] := by
  decide +kernel

theorem rows16059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16059 = true := by
  decide +kernel

theorem tot16059 : totK PD2M8K2 D2M8K2.t16059 = [0, 193167717871, 463097588653, 214269404475, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
