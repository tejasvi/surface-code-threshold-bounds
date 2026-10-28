import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5696 = true := by
  decide +kernel

theorem tot5696 : totK PD2M8K2 D2M8K2.t5696 = [0, 0, 0, 321337202268, 451850678649, 75544887691, 0, 0] := by
  decide +kernel

theorem rows5697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5697 = true := by
  decide +kernel

theorem tot5697 : totK PD2M8K2 D2M8K2.t5697 = [0, 0, 244623093625, 496291544073, 151733145617, 8323569078, 0, 0] := by
  decide +kernel

theorem rows5698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5698 = true := by
  decide +kernel

theorem tot5698 : totK PD2M8K2 D2M8K2.t5698 = [0, 0, 169019080520, 459799389509, 212383266048, 15888650024, 0, 0] := by
  decide +kernel

theorem rows5699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5699 = true := by
  decide +kernel

theorem tot5699 : totK PD2M8K2 D2M8K2.t5699 = [0, 0, 226705665078, 487490002231, 163032326069, 7414397321, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
