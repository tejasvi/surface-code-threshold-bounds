import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6984 = true := by
  decide +kernel

theorem tot6984 : totK PD2M8K2 D2M8K2.t6984 = [0, 153535237595, 468832638181, 251546097127, 14013976962, 0, 0, 0] := by
  decide +kernel

theorem rows6985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6985 = true := by
  decide +kernel

theorem tot6985 : totK PD2M8K2 D2M8K2.t6985 = [0, 153064571496, 436029812485, 273785378904, 21711443188, 0, 0, 0] := by
  decide +kernel

theorem rows6986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6986 = true := by
  decide +kernel

theorem tot6986 : totK PD2M8K2 D2M8K2.t6986 = [0, 0, 277357998344, 495932632008, 103693855173, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6987 = true := by
  decide +kernel

theorem tot6987 : totK PD2M8K2 D2M8K2.t6987 = [0, 162444838759, 409283633965, 318388529238, 40625277319, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
