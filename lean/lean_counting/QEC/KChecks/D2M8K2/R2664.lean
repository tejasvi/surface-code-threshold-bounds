import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10656 = true := by
  decide +kernel

theorem tot10656 : totK PD2M8K2 D2M8K2.t10656 = [0, 0, 168495598459, 463650846439, 233614599362, 13494115512, 0, 0] := by
  decide +kernel

theorem rows10657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10657 = true := by
  decide +kernel

theorem tot10657 : totK PD2M8K2 D2M8K2.t10657 = [0, 0, 198860157886, 478319461364, 215896016606, 11066126582, 0, 0] := by
  decide +kernel

theorem rows10658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10658 = true := by
  decide +kernel

theorem tot10658 : totK PD2M8K2 D2M8K2.t10658 = [0, 0, 188117719910, 475678256127, 223517672698, 12443528988, 0, 0] := by
  decide +kernel

theorem rows10659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10659 = true := by
  decide +kernel

theorem tot10659 : totK PD2M8K2 D2M8K2.t10659 = [0, 0, 174768765716, 478488111422, 225486611754, 15401492952, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
