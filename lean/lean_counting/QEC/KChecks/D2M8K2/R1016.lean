import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4064 = true := by
  decide +kernel

theorem tot4064 : totK PD2M8K2 D2M8K2.t4064 = [0, 81647540556, 249946000813, 377726513403, 178115567687, 8209931632, 0, 0] := by
  decide +kernel

theorem rows4065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4065 = true := by
  decide +kernel

theorem tot4065 : totK PD2M8K2 D2M8K2.t4065 = [0, 183101924924, 468224516628, 256679403745, 22983913760, 0, 0, 0] := by
  decide +kernel

theorem rows4066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4066 = true := by
  decide +kernel

theorem tot4066 : totK PD2M8K2 D2M8K2.t4066 = [0, 175351648363, 471125230480, 246129363824, 13535101234, 0, 0, 0] := by
  decide +kernel

theorem rows4067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4067 = true := by
  decide +kernel

theorem tot4067 : totK PD2M8K2 D2M8K2.t4067 = [0, 0, 284020278913, 513132507213, 108459156107, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
