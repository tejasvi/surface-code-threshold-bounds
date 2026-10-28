import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9792 = true := by
  decide +kernel

theorem tot9792 : totK PD2M8K2 D2M8K2.t9792 = [0, 0, 172965868247, 463316877922, 207622465551, 10939763223, 0, 0] := by
  decide +kernel

theorem rows9793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9793 = true := by
  decide +kernel

theorem tot9793 : totK PD2M8K2 D2M8K2.t9793 = [0, 0, 178859015385, 477558349977, 222076721477, 12590956490, 0, 0] := by
  decide +kernel

theorem rows9794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9794 = true := by
  decide +kernel

theorem tot9794 : totK PD2M8K2 D2M8K2.t9794 = [0, 0, 193541232650, 467846562405, 208292695291, 8223539398, 0, 0] := by
  decide +kernel

theorem rows9795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9795 = true := by
  decide +kernel

theorem tot9795 : totK PD2M8K2 D2M8K2.t9795 = [0, 50669764256, 201283830445, 404214525897, 229778245727, 17433533548, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
