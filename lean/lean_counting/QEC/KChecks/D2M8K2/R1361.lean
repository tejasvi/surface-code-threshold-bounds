import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5444 = true := by
  decide +kernel

theorem tot5444 : totK PD2M8K2 D2M8K2.t5444 = [0, 0, 134594811169, 407134534172, 347343146304, 43428564475, 0, 0] := by
  decide +kernel

theorem rows5445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5445 = true := by
  decide +kernel

theorem tot5445 : totK PD2M8K2 D2M8K2.t5445 = [0, 0, 193438026046, 487274370061, 221937228888, 13614186330, 0, 0] := by
  decide +kernel

theorem rows5446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5446 = true := by
  decide +kernel

theorem tot5446 : totK PD2M8K2 D2M8K2.t5446 = [0, 0, 88459214294, 382169665492, 357353214216, 75245052441, 9987233462, 0] := by
  decide +kernel

theorem rows5447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5447 = true := by
  decide +kernel

theorem tot5447 : totK PD2M8K2 D2M8K2.t5447 = [0, 0, 0, 158871470601, 458885507097, 261957202962, 14744583621, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
