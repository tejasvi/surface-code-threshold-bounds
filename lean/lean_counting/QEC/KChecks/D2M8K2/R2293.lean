import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9172 = true := by
  decide +kernel

theorem tot9172 : totK PD2M8K2 D2M8K2.t9172 = [0, 170813767808, 466085926597, 218886099077, 14157404409, 0, 0, 0] := by
  decide +kernel

theorem rows9173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9173 = true := by
  decide +kernel

theorem tot9173 : totK PD2M8K2 D2M8K2.t9173 = [0, 168656360481, 456926263575, 226159385267, 12709741089, 0, 0, 0] := by
  decide +kernel

theorem rows9174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9174 = true := by
  decide +kernel

theorem tot9174 : totK PD2M8K2 D2M8K2.t9174 = [0, 0, 271599245128, 474099111548, 110293896184, 1369150432, 0, 0] := by
  decide +kernel

theorem rows9175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9175 = true := by
  decide +kernel

theorem tot9175 : totK PD2M8K2 D2M8K2.t9175 = [0, 136056719320, 427762242402, 284986769970, 27324221032, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
